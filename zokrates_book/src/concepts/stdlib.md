## Standard library

ZoKrates comes with a number of reusable components. For now, these components are:

### sha256

```zokrates
import "LIBSNARK/sha256"
```

A function that takes 512 field elements as inputs, checks that they are all bits, and returns their sha256 hash as 256 field elements.

### sha256compression

```zokrates
import "LIBSNARK/sha256compression"
```

A function that takes 512 field elements as inputs, checks that they are all bits, and returns the result of applying the sha256 compression function on them. The difference with `sha256` is that no padding is added at the end of the message, which makes it more efficient but also less compatible with Solidity.

### sha256packed

```zokrates
import "LIBSNARK/sha256packed"
```

A function that takes 4 field elements as inputs, unpacks each of them to 128 bits (big endian), concatenates them and applies sha256. It then returns two field elements, each representing 128 bits of the result.

### pack128

```zokrates
import "PACKING/pack128"
```

Packs 128 field elements as one.

### unpack128

```zokrates
import "PACKING/unpack128"
```

Unpacks a field element to 128 field elements.