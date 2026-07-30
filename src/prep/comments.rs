fn is_line_comment(chars: &[char], i: usize) -> bool {
    i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '/'
}

fn is_block_comment(chars: &[char], i: usize) -> bool {
    i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '*'
}

fn handle_line_comment(chars: &[char], i: &mut usize, output: &mut String) {
    // Already checked by caller — we know it's a line comment
    while *i < chars.len() && chars[*i] != '\n' {
        output.push(' ');
        *i += 1;
    }
}

fn handle_block_comment(chars: &[char], i: &mut usize, output: &mut String) {
    // Already checked by caller — we know it's a block comment.
    // The delimiters are blanked like any other comment character so the
    // output stays the same length as the input, column for column.
    output.push_str("  ");
    *i += 2;
    while *i < chars.len() {
        if *i + 1 < chars.len() && chars[*i] == '*' && chars[*i + 1] == '/' {
            output.push_str("  ");
            *i += 2;
            return;
        }
        // Unterminated comments fall out of the loop at end of input, blanking
        // every character on the way — including a trailing newline.
        if chars[*i] == '\n' {
            output.push('\n');
        } else {
            output.push(' ');
        }
        *i += 1;
    }
}

pub fn strip_comments(input: &str) -> String {
    let mut output = String::with_capacity(input.len());
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if is_line_comment(&chars, i) {
            handle_line_comment(&chars, &mut i, &mut output);
            continue;
        }
        if is_block_comment(&chars, i) {
            handle_block_comment(&chars, &mut i, &mut output);
            continue;
        }
        output.push(chars[i]);
        i += 1;
    }

    output
}

