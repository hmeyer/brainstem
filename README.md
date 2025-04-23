# Thalamus

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A compiler and interpreter for Brainfuck and its high-level extensions, written in Rust.

## Project Overview

Thalamus is a two-stage compilation system:

```
Thalamus (high level) -> BrainStem (low-level) → Brainfuck → (optional Brainfuck runtime)
```

## BrainStem Language

BrainStem is a low level language and compiler.
It supports variables, arithmetic and boolean expressions, conditionals, loops, stackframe handling and linear memory access.
BrainStem gets compiled to Brainfuck.

### Features

#### Variables and Arrays
```brainstem
var x = 42;          // Declare a variable
var arr[] = [1,2,3]; // Declare an array
var str[] = "abc";   // String arrays
```

#### Arithmetic Operations
```brainstem
var sum = a + b;
var product = x * y;
var quotient = n / m;
var remainder = n % m;
```

#### Conditional Logic
```brainstem
if x > 0 then {
    putc("+");
} else {
    putc("-");
}
```

#### Loops
```brainstem
while condition {
    // body
}
```

#### Stack Frame Handling
```brainstem
// Push a stack frame with modified variables
PushStackFrame(x=x+1);
// Do something in the new context
PopStackFrame();
```

### Basic Example
```
var x = 5;
putc("0" + x);  # Will print 5
```

## Building and Usage

### Prerequisites
- Rust Edition 2024

### Building
```bash
cargo build --release
```

### Running a BrainStem Program
```bash
cargo run -- --input program.bs --run
```

### Compile Only (Output Brainfuck)
```bash
cargo run -- --input program.bs --output program.bf
```

### Running with Different Integer Types
```bash
cargo run -- --input program.bs --run --int-type i32
```

### Running Examples
```bash
# Run the hello world example
cargo run -- --input examples/hello_world.bs --run

# Run factorial example with larger integer type
cargo run -- --input examples/factorial.bs --run --int-type i32
```

## Examples

In the `examples` directory you'll find several BrainStem programs that demonstrate the language features:

- **hello_world.bs**: Basic "Hello, World!" program
- **factorial.bs**: Calculates factorial of a number
- **fibonacci.bs**: Generates Fibonacci sequence
- **number_printer.bs**: Recursive implementation of a decimal number printer

These examples also serve as end-to-end tests for the compiler and runtime.

## Thalamus (TBD)

This is the name of the high level language and compiler.
Thalamus adds features like function calls, an allocator and a lot of syntatic sugar.
Thalamus gets compiled to BrainStem.

## License

This project is licensed under the MIT License - see the LICENSE file for details.
