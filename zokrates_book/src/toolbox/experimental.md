# Experimental features

ZoKrates supports some experimental features.

## Nova

ZoKrates supports the `nova` proof system using the `bellperson` backend. Nova is accessed with the subcommand `nova`.

### API

To use Nova, programs must have the following signature, for any types `State` and `StepInput`:

```
def main(public State state, private StepInput step_input) -> State
```

Then, using Nova lets the user prove many steps of this program, given an initial state.

For example:

```
{{#include ../../../zokrates_cli/examples/book/nova_step.zok}}
```

We compile this program using the Pallas curve:

```bash
zokrates compile -i sum.zok --curve pallas
```

Then we can prove three iterations as follows:

```bash
echo "\"0\"" > init.json
echo "[\"1\", \"7\", \"42\"]" > steps.json
zokrates nova prove
```

The proof created at `proof.json` proves the statement `0 + 1 + 7 + 42 == 50`.

We can extend it by running more steps, for example with the same intermediate inputs:

```
zokrates nova prove --continue
```

The proof updated at `proof.json` proves the statement `50 + (0 + 1 + 7 + 42) == 100`.

Once we're done, we compress the proof to a compressed snark:

```
zokrates nova compress
```

Finally, we can verify this proof

```
zokrates nova verify
```

### Limitations

- The step circuit must be compiled with `--curve pallas`
- The resulting recursive proof cannot currently be verified on the EVM