# File structure and lexical rules

A `.vest` file is a sequence of top-level definitions in any order: format
definitions, constant definitions, macro definitions, and at most one byte-order (endianness) directive.

## Identifiers and reserved words

Identifiers start with a letter or `_` and continue with letters, digits, or
`_`. Format names, field names, and enum variants all use this form.

These words are reserved and cannot be used as identifiers:

```text
macro   const   enum   choose   wrap
Option  Vec     Tail   Nothing  Never
btc_varint      uleb128
```

Integer type names are also reserved: any `u` or `i` followed by digits, so
`u8`, `u16`, `u3`, `i32` and so on are unavailable as names.

The following identifier forms have extra syntax:

| Form           | Meaning                                                                 |
| -------------- | ----------------------------------------------------------------------- |
| `@name`        | a dependency reference — a field bound with `@`, usable in later fields |
| `@name.member` | dotted access into a dependency's field, nested arbitrarily deep        |
| `_`            | the wildcard branch of a `choose`                                       |

## Comments

Only line comments exist:

```vest,ignore
// this is a comment
```

There is *no* block comment syntax (`/* ... */`).

## Byte order

```vest,ignore
!BIG_ENDIAN
```

or

```vest,ignore
!LITTLE_ENDIAN
```

Note:
- **Little-endian is the default.** A file with no directive is little-endian.
- **The directive is file-global, wherever it appears.** Putting `!BIG_ENDIAN`
  on the last line still applies it to every definition in the file.

Byte order applies only where it is meaningful: multi-byte integers. It does not
affect `u8`, byte arrays, or an 8-bit `bits` block.

## Integer literals

There are three forms, usable anywhere a constant integer is expected — enum values,
constraints, constant fields, array lengths:

| Form            | Example         | Notes                 |
| --------------- | --------------- | --------------------- |
| decimal         | `15213`         |                       |
| hexadecimal     | `0x3F`, `0x5a`  | `0x` prefix required  |
| ASCII character | `'a'`, `'\x1b'` | one byte, value 0–255 |

Similar to Rust, enum values may carry a type suffix that fixes the underlying representation:

```vest
kind = enum { A = 0u16, B = 1u16, }
```

## Constant arrays

Byte-array constants take either a string or a list form, and the list form has
a repeat shorthand:

```vest
const MAGIC: [u8; 4] = "vest"
const ZEROS: [u8; 4] = [0; 4]
const BYTES: [u8; 3] = [0x01, 0x02, 0x03]
```

## Whitespace

Whitespace, including newlines, is insignificant. Fields and enum variants are
comma-terminated — including the last one:

```vest
msg = {
    a: u8,
    b: u16,     // trailing comma required
}
```

## Vim and Neovim highlighting

The repository includes [`vest/vest.vim`](https://github.com/secure-foundations/vest/blob/main/vest/vest.vim).
Copy it to `~/.vim/syntax/vest.vim` (or
`~/.config/nvim/syntax/vest.vim`) and add this to your Vim configuration:

```vim
autocmd BufRead,BufNewFile *.vest setfiletype vest
```
