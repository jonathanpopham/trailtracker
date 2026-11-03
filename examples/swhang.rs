use trailtracker::lang::swift::lexer::lex;
fn main() {
    for (i, src) in [
        "func f(x: Int) -> Int {\n    return x\n}\n",
        "class C {\n    var n = 0\n}\n",
        "let x = 0xFF_00 + 1.5e3 + 0x1.8p2\n",
        "let s = \"hi \\(name)!\" + \"\"\"\nmulti\nline\n\"\"\"\n",
        "let r = #\"raw \\#(x) \" still\"# + ##\"two #\"## \n",
        "// line\n/* block /* nested */ end */\nstruct S {}\n",
        "let \u{3bb} = \"\u{2603} \u{20ac}\" // unicode\n",
        "a ..< b ... c ?? d === e\n",
        "let `class` = 1; print($0)\n",
        "#!/usr/bin/swift\nprint(\"hi\")\n",
    ]
    .iter()
    .enumerate()
    {
        eprintln!("INPUT[{i}]: {src:?}");
        let n = lex(src).len();
        eprintln!("  -> {n} tokens OK");
    }
    eprintln!("ALL DONE");
}
