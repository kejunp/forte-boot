// since mangled names are original_name_type_type_type...... In the original
// name, change all underscores to U

pub fn prep_mangle(input: char) -> char {
    if input == '_' {
        return 'U';
    } else {
        return input;
    }
}
