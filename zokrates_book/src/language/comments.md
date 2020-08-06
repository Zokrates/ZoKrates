## Comments

## Inline comments
Inline (single-line) comments allow narrative on only one line at a time. Single-line comments can begin in any column of a given line and end at a new line or carriage return. Inline comments can be added with double-slashes.

```zokrates
{{#include ../../../zokrates_cli/examples/book/comments.zok}}
```

## Multi-line comments
Multi-line comments have one or more lines of narrative within a set of comment delimiters. The `/*` delimiter marks the beginning of the comment, and the `*/` marks the end. Any content between those delimiters is considered a comment.

```zokrates
{{#include ../../../zokrates_cli/examples/book/multiline_comments.zok}}
```