## Standard library

>**! The standard library is currently being refactored !**  

> Currently the standard library is split into two parts:
> * Global imports: these functions can be imported without specifying the correct path
> * Relative imports: these functions need the the correct relative path on the file-system

ZoKrates comes with a number of reusable components. For now, these components are:

### Global imports

#### pack128

```zokrates
import "PACKING/pack128"
```

Packs 128 field elements as one.

#### unpack128

```zokrates
import "PACKING/unpack128"
```
Unpacks a field element to 128 field elements.

### Relative import
>Caution: In order to import these functions the correct relative path with respect to the zokrates binary need to be specified.

The standard library is located at `./stdlib/` in the ZoKrates root folder. Is solely based on the ZoKrates DSL and can be easily extended.

#### sha256

```zokrates
import "./stlib/512_padded.code"
```

A function that takes 2 `field[256]` arrays as inputs and returns their sha256 compression function as an array of 256 field elements.

#### sha256compression

```zokrates
import "./stlib/512.code"
```

A function that takes 2 `field[256]` arrays as inputs and returns their sha256 compression function as an array of 256 field elements.
The difference with `sha256` is that no padding is added at the end of the message, which makes it more efficient but also less compatible with Solidity.

There also is support for 2round (1024bit input) and and 3 round (1536bit input) variants, using  `./stlib/1024.code` or `./stlib/1536.code` respectively.

#### sha256packed

```zokrates
import "./stlib/512_packed.code"
```

A function that takes 4 field elements as inputs, unpacks each of them to 128 bits (big endian), concatenates them and applies sha256. It then returns two field elements, each representing 128 bits of the result.

