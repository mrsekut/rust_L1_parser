mod error;
mod lexer;
mod parser;
use std::error::Error;
use std::io;

fn prompt(s: &str) -> io::Result<()> {
    use std::io::{stdout, Write};

    let stdout = stdout();
    let mut stdout = stdout.lock();
    stdout.write(s.as_bytes())?;
    stdout.flush()
}

fn main() {
    use std::io::{stdin, BufRead, BufReader};

    let stdin = stdin();
    let stdin = stdin.lock();
    let stdin = BufReader::new(stdin);
    let mut lines = stdin.lines();

    loop {
        prompt("> ").unwrap();
        if let Some(Ok(line)) = lines.next() {
            let ast = match line.parse::<parser::Ast>() {
                Ok(ast) => ast,
                Err(e) => {
                    eprintln!("{}", e);
                    let mut source = e.source();
                    while let Some(e) = source {
                        eprintln!("caused by {}", e);
                        source = e.source()
                    }
                    continue;
                }
            };
            println!("{:?}", ast);
        } else {
            break;
        }
    }
}
