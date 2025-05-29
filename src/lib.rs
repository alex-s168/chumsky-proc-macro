use proc_macro2::TokenTree;
use chumsky::{extra::ParserExtra, input::ValueInput, label::LabelError, util::MaybeRef, IterParser, Parser};

pub trait LikeTokenTree {
    fn as_tok(&self) -> &TokenTree;
}

impl LikeTokenTree for TokenTree {
    fn as_tok(&self) -> &TokenTree {
        self
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum Expected
{
    StandAlonePunct(char),
    PunctSeq(String),
    Ident,
}

impl<T> From<Expected> for chumsky::error::RichReason<'_, T> {
    fn from(value: Expected) -> Self {
        chumsky::error::RichReason::Custom(format!("{:?}", value))
    }
}

/// A single punctuation character like `+`, `-` or `#`.
pub fn punct<'src, I, E>(val: char) -> impl Parser<'src, I, (), E>
where
    I: ValueInput<'src>,
    I::Token: LikeTokenTree + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, Expected>,
{
    punct_impl(val)
}

fn punct_impl<'src, I, E>(val: char) -> impl Parser<'src, I, (), E>
where
    I: ValueInput<'src>,
    I::Token: LikeTokenTree + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, Expected>,
{
    use chumsky::prelude::*;
    any().try_map(move |x: I::Token, span| {
        match &x.as_tok() {
            TokenTree::Punct(p) => {
                // disabled spacing check because proc macro sucks
                if /*p.spacing() == spacing &&*/ p.as_char() == val {
                    Some(())
                } else {
                    None
                }
            }

            _ => None
        }.ok_or_else(|| LabelError::expected_found(
                [Expected::StandAlonePunct(val)],
                Some(MaybeRef::Val(x)),
                span))
    })
}

/// A sequence of punctuation character like `+=`, '--', or even `#<##>`.
pub fn punct_seq<'src, I, E, S: AsRef<str>>(seq: S) -> impl Parser<'src, I, (), E>
where
    I: ValueInput<'src>,
    I::Token: LikeTokenTree + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, Expected>,
{
    use chumsky::prelude::*;

    let seq = seq.as_ref().to_string();
    assert!(!seq.len() >= 2);

    seq.chars()
        .map(|val| punct_impl(val)
             .boxed())
        .reduce(|a,b| a.then_ignore(b).boxed()).unwrap_or(empty().boxed())
            .map_err_with_state(move |_,span,_| LabelError::expected_found(
                        [Expected::PunctSeq(seq.clone())],
                        None,
                        span))
}

pub fn ident<'src, I, E>() -> impl Parser<'src, I, String, E>
where
    I: ValueInput<'src>,
    I::Token: LikeTokenTree + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, Expected>
{
    use chumsky::prelude::*;

    any().try_map(move |x: I::Token, span| match &x.as_tok() {
        TokenTree::Ident(i) => Some(i.to_string()),
        _ => None
    }.ok_or_else(|| LabelError::expected_found(
            [Expected::Ident],
            Some(MaybeRef::Val(x)),
            span)))
}

pub fn namespace_with_ident<'src, I, E>()  -> impl IterParser<'src, I, String, E>
where
    I: ValueInput<'src>,
    I::Token: LikeTokenTree + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, Expected>
{
    use chumsky::prelude::*;

    ident()
        .separated_by(punct_seq("::"))
        .at_least(1)
}

/// A literal character (`'a'`), string (`"hello"`), number (`2.3`), etc.
pub fn literal<'src, I, E>() -> impl Parser<'src, I, String, E>
where
    I: ValueInput<'src>,
    I::Token: LikeTokenTree + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, Expected>
{
    use chumsky::prelude::*;

    any().try_map(move |x: I::Token, span| match &x.as_tok() {
        TokenTree::Literal(i) => Some(i.to_string()),
        _ => None
    }.ok_or_else(|| LabelError::expected_found(
            [Expected::Ident],
            Some(MaybeRef::Val(x)),
            span)))
}

pub enum GroupDelim {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
}

impl GroupDelim {
    fn to_procmacro(&self) -> proc_macro2::Delimiter {
        match self {
            GroupDelim::Brace => proc_macro2::Delimiter::Brace,
            GroupDelim::Bracket => proc_macro2::Delimiter::Bracket,
            GroupDelim::Parenthesis => proc_macro2::Delimiter::Parenthesis,
        }
    }
}

pub trait ParserGroupedExtension<'src, V, E>:
    Parser<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>, V, E> + Sized
where
    E: ParserExtra<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>>,
    E::Context: Default,
    E::State: Default,
    E::Error: LabelError<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>, Expected>
{
    fn grouped(self, delim: GroupDelim) -> impl Parser<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>, V, E> 
    {
        use chumsky::prelude::*;
        use chumsky::input::Stream;

        any().try_map(move |x: proc_macro2::TokenTree, span| match &x.as_tok() {
            TokenTree::Group(i) if i.delimiter() == delim.to_procmacro() => {
                self.parse(Stream::from_iter(i.stream().into_iter()))
                    .into_result()
                    .map_err(|x| x.into_iter().next().unwrap())
            }
            _ => Err(LabelError::expected_found(
                [Expected::Ident],
                Some(MaybeRef::Val(x)),
                span)) 
        })
    }
}

impl<'src, V, E, P> ParserGroupedExtension<'src, V, E> for
    P 
where
    P: Parser<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>, V, E> + Sized,
    E: ParserExtra<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>>,
    E::Context: Default,
    E::State: Default,
    E::Error: LabelError<'src, chumsky::input::Stream<proc_macro2::token_stream::IntoIter>, Expected>
{}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    use chumsky::{extra::Err, input::Stream, prelude::*};

    #[test]
    fn test_punct() {
        let toks = quote! { + }.into_iter();

        let parser = &punct::<_, Err<Simple<_>>>('+');
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_punct2() {
        let toks = quote! { += }.into_iter();

        let parser = &punct::<_, Err<Simple<_>>>('+');
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap_err();
    }

    #[test]
    fn test_punct_seq() {
        let toks = quote! { --> }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("-->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_punct_seq2() {
        let toks = quote! { -> }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("-->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap_err();
    }

    #[test]
    fn test_punct_seq3() {
        let toks = quote! { --># }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("-->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap_err();
    }

    #[test]
    fn test_punct_seq4() {
        let toks = quote! { ---> }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("-->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap_err();
    }

    #[test]
    fn test_punct_seq5() {
        let toks = quote! { -> }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_punct_seq6() {
        let toks = quote! { ->< }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("->").then(punct('<'));
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_punct_seq7() {
        let toks = quote! { ---> }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("--->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_punct_seq8() {
        let toks = quote! { ++++ }.into_iter();

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("++++");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_ident0() {
        let toks = quote! { hello_world }.into_iter();

        let parser = &ident::<_, Err<Simple<_>>>();
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_ident1() {
        let toks = quote! { 1 2 3 }.into_iter();

        let parser = &ident::<_, Err<Simple<_>>>();
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap_err();
    }

    #[test]
    fn test_namespace_indent() {
        let toks = quote! { hello::world::test }.into_iter();

        let parser = &namespace_with_ident::<_, Err<Simple<_>>>().collect::<Vec<_>>();
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_literal() {
        let toks = quote! { "hey" }.into_iter();

        let parser = &literal::<_, Err<Simple<_>>>();
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_group() {
        let toks = quote! { hello (world::x) }.into_iter();

        let parser = &namespace_with_ident::<_, Err<Simple<_>>>()
            .collect::<Vec<_>>()
            .then(namespace_with_ident().collect::<Vec<_>>()
                .grouped(GroupDelim::Parenthesis));
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

}
