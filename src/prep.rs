mod comments;

// Comments only, blanked to spaces so later characters keep their line and
// column. Mangling belongs to codegen; see docs/prose.txt on `@symbol`.
pub fn preprocess(input: &str) -> String {
    comments::strip_comments(input)
}
