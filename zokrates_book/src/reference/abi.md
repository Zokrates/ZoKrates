# ZoKrates ABI

In order to interact programatically with compiled ZoKrates programs, ZoKrates supports passing arguments using an ABI.

To illustrate this, we'll use the following example program:

```
struct Bar {
    field a
}

struct Foo {
    field a
    Bar b
}

def main(private Foo foo, bool[2] bar, field num) -> (field):
	return 42
```

## ABI specification

When compiling a program, an ABI specification is generated and describes the interface of the program.

In this example, the ABI specification is:

```json
{
    "inputs": [
        {
            "name": "foo",
            "public": false,
            "type": "struct",
            "components": [ 
                {
                    "name": "a",
                    "type": "field"
                },
                {
                    "name": "b",
                    "type": "struct",
                    "components": [
                        {
                            "name": "a",
                            "type": "field"
                        }
                    ]
                }
            ]
        },
        { 
            "name": "bar",
            "public": "true",
            "type": "array",
            "components": {
                "size": 2,
                "type": "bool"
            }
        },
        { 
            "name": "num",
            "public": "true",
            "type": "field"
        }
    ],
    "outputs": [
        {
            "type": "field"
        }
    ]
}
```


## ABI input format

When executing a program, arguments can be passed as a JSON object of the following form:

```json
[
    {
        "a": "42",
        "b": 
        {
            "a": "42"
        }
    },
    [
        true,
        false
    ],
    "42"
]
```

Note that field elements are passed as JSON strings in order to support arbitrary large numbers.