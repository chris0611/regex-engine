use regex_engine::match_pattern;

fn main() {
    let pattern = r"\w+\d";
    let input = "abcd2";

    println!("Pattern: {}", pattern);
    println!("Input: {}", input);
    match match_pattern(pattern, input) {
        Ok(result) => println!("Pattern matches: {}", result),
        Err(e) => println!("Error: {}", e),
    }
}
