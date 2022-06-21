# ZoKrates ABI

In order to interact programatically with compiled ZoKrates programs, ZoKrates supports passing arguments using an ABI.

To illustrate this, we'll use the following example program:

```
{{#include ../../../zokrates_cli/examples/book/abi.zok}}
```

## ABI specification

When compiling a program, an ABI specification is generated and describes the interface of the program.

In this example, the ABI specification is:

```json
{
   "inputs":[
      {
         "name":"foo",
         "public":true,
         "type":"struct",
         "components":{
            "name":"Foo",
            "members":[
               {
                  "name":"a",
                  "type":"u8"
               },
               {
                  "name":"b",
                  "type":"struct",
                  "components":{
                     "name":"Bar",
                     "members":[
                        {
                           "name":"a",
                           "type":"field"
                        }
                     ]
                  }
               }
            ]
         }
      },
      {
         "name":"bar",
         "public":true,
         "type":"array",
         "components":{
            "size":2,
            "type":"bool"
         }
      },
      {
         "name":"num",
         "public":true,
         "type":"field"
      }
   ],
   "output": {
     "type":"field"
   }
}
```


## ABI input format

When executing a program, arguments can be passed as a JSON object of the following form:

```json
[
   {
      "a":"0x2a",
      "b":{
         "a":"42"
      }
   },
   [
      true,
      false
   ],
   "42"
]
```

Note the following:
- Field elements are passed as JSON strings in order to support arbitrary large numbers
- Unsigned integers are passed as JSON strings containing their hexadecimal representation
- Structs are passed as JSON objects, ignoring the struct name