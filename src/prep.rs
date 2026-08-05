mod comments;

/// What is done to a source before the lexer reads it.
///
/// Comments only. The lexer has no case for the `/` that opens one, so they
/// are blanked out -- to spaces, not deleted, so that every later character
/// keeps its line and column and a diagnostic can quote the source as it was
/// written while the parse runs on this copy.
///
/// Mangling used to be done here as well, and then on identifier tokens, and
/// is now neither: a symbol's name is settled from a declaration that has been
/// resolved and typed, which is a thing only codegen holds. See docs/prose.txt
/// on `@symbol`.
pub fn preprocess(input: &str) -> String {
    return comments::strip_comments(input);
}
