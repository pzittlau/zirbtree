# ZiRBTree

Intrusive [Red-Black Trees](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree) for [Zig](https://ziglang.org/).

There are a generic and a non-generic implementation. 

The generic one is generally easier to use as you just need one comparison function and just have to
provide it once. But of course the code is generated for each different specialization.

The non-generic one is not as ergonomic because of the need of `@fieldParentPtr` to access the
containing struct, but allows for cases when a single node is part of multiple trees without long
hierarchy chains, that would be created by the generic one. It's also just compiled one time instead
of once for each different specialization.

## Installation

Just vendor the files and import them as necessary.

## Examples

`main_generic.zig` is an example demonstrating the usage of the generic Red-Black Tree and
`main.zig` shows usage of the non-generic Red-Black Tree. You can also look at the tests in the
implementation files.

You can run these examples using `zig run main_generic.zig` and `zig run main.zig` respectively.

## License

The code is licensed under MIT.
