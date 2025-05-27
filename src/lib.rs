use proc_macro2::TokenTree;
use chumsky::{extra::ParserExtra, input::ValueInput, label::LabelError, util::MaybeRef, Parser};

pub trait LikeTokenTree {
    fn as_tok(&self) -> &TokenTree;
}

impl LikeTokenTree for TokenTree {
    fn as_tok(&self) -> &TokenTree {
        self
    }
}

#[non_exhaustive]
pub enum Expected
{
    StandAlonePunct(char),
    PunctSeq(String)
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
        println!("{:?}", toks);

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("--->");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }

    #[test]
    fn test_punct_seq8() {
        let toks = quote! { ++++ }.into_iter();
        println!("{:?}", toks);

        let parser = &punct_seq::<_, Err<Simple<_>>, _>("++++");
        let _v = parser.parse(Stream::from_iter(toks))
            .into_result()
            .unwrap();
    }
}
