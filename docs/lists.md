# Lists

## Syntax

- Nonempty list literal: `[ expr (, expr)* ]`
- Empty list literal: `[] : type`
- Cons: `expr :: expr`
- Head: `head expr`
- Tail: `tail expr`
- Length: `length expr`

## Static semantics

- If `x1 : T`, `x2 : T`, ..., `xn : T` then `[x1, x2, ..., xn] : list(T)`
- `([] : list(T)) : list(T)`
- If `x : T` and `xs : list(T)` then `(x :: xs) : list(T)`
- If `xs : list(T)` then `head xs : T` and `tail xs : list(T)`
- If the maximum list length is `N` and `n = floor(log_2(N)) + 1` (the number of bits required to express `N`) then `length xs : int(n)`

## Dynamic semantics

- `[x1, x2, ..., xn]` returns a list of `n` elements containing `x1`, `x2`, ..., `xn`.
- `[] : T` returns an empty list.
- `x :: xs` returns `x` added to the front of `xs`. If this exceeds the maximum list length then the last element in `xs` will be dropped from the result.
- `head xs` returns the first element of `xs` and `tail xs` returns all but the first element of `xs`. If `xs` is empty then there will be no result (similar to `observe false`).
- `length xs` returns the length of `xs`.

## Maximum list length

The maximum list length `N` is a bound on the length of lists during execution of the program. If the final result is a list, then the probability distribution shown will be over all lists of length at most `N`.

The maximum list length can be set with the command line flag `-max-list-length N`. `N` must be an integer which is at least 1. If not specified, it defaults to the recursion limit, which if not specified defaults to 10.
