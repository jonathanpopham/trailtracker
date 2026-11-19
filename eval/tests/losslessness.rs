//! Exhaustive execution of the parser proof's entire bounded input domain.
use trailtracker::lang::rust::parser::parse;
use trailtracker_eval::losslessness::{ALPHABET, MAX_LEN};

#[test]
fn every_bounded_parser_input_round_trips() {
    let mut checked = 0;
    let mut bytes = [0; MAX_LEN];
    for len in 0..=MAX_LEN {
        for mut index in 0..ALPHABET.len().pow(len as u32) {
            for byte in &mut bytes[..len] {
                *byte = ALPHABET[index % ALPHABET.len()];
                index /= ALPHABET.len();
            }
            let source = std::str::from_utf8(&bytes[..len]).unwrap();
            let tree = parse("kani.rs", source);
            let mut rebuilt = String::new();
            tree.root.reconstruct(source, &mut rebuilt);
            assert_eq!(rebuilt, source, "input bytes: {:?}", &bytes[..len]);
            checked += 1;
        }
    }
    assert_eq!(checked, 1_508_598);
    println!("Exhaustively checked {checked} parser inputs (lengths 0..={MAX_LEN}).");
}
