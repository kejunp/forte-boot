//! The text a diagnostic quotes from, and what it is called.

/// A source to be quoted: its name, and the characters it is made of.
///
/// Borrowed rather than owned, because by the time anything is being reported
/// the text is already being held by whichever phase read it, and a diagnostic
/// wants to quote it rather than to keep it. Building one costs nothing, so a
/// phase makes one where it reports and forgets it afterward.
///
/// Characters and not bytes: a column counts characters, and the two agree
/// only for as long as a source stays ASCII.
pub struct Source<'a> {
    path: &'a str,
    text: &'a [char],
}

impl<'a> Source<'a> {
    pub fn new(path: &'a str, text: &'a [char]) -> Source<'a> {
        Source { path, text }
    }

    /// What to call it in a `--> path:line:col`.
    pub fn path(&self) -> &str {
        self.path
    }

    /// The `line`th line, counted from one and without its newline.
    ///
    /// `None` where there is no such line. That is a diagnostic pointing past
    /// the end of the source rather than a diagnostic that is wrong: a file
    /// ending in a newline has an empty last line, and the end of the file is
    /// the column after the last character written.
    pub fn line(&self, line: usize) -> Option<String> {
        if line == 0 {
            return None;
        }
        let mut at = 1;
        let mut text = String::new();
        for &c in self.text {
            if at > line {
                break;
            }
            if c == '\n' {
                at += 1;
                continue;
            }
            if at == line {
                text.push(c);
            }
        }
        if at < line {
            return None;
        }
        Some(text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chars(s: &str) -> Vec<char> {
        s.chars().collect()
    }

    #[test]
    fn reads_a_line_by_number() {
        let text = chars("one\ntwo\nthree\n");
        let source = Source::new("t.fc", &text);
        assert_eq!(source.line(1).as_deref(), Some("one"));
        assert_eq!(source.line(2).as_deref(), Some("two"));
        assert_eq!(source.line(3).as_deref(), Some("three"));
        // The newline at the end opens a fourth line, and it is empty. That is
        // where a diagnostic about the end of the file points.
        assert_eq!(source.line(4).as_deref(), Some(""));
        assert_eq!(source.line(5), None);
        assert_eq!(source.line(0), None);
    }

    /// A source whose last line was never ended still has that line.
    #[test]
    fn a_file_that_ends_without_a_newline_still_ends_somewhere() {
        let text = chars("one\ntwo");
        let source = Source::new("t.fc", &text);
        assert_eq!(source.line(2).as_deref(), Some("two"));
        assert_eq!(source.line(3), None);
    }
}
