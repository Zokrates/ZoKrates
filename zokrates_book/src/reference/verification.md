# Verification

Passed to the verifier contract, this proof can be checked.
For example, using `web3`, a call would look like the following:

```
Verifier.at(<verifier contract address>).verifyTx(A, A_p, B, B_p, C, C_p, H, K, [...publicInputs, ...outputs])
```

Where `A, ..., K` are defined as above (adding brackets and quotes: `A = ["0x123", "0x345"]`), `publicInputs` are the public inputs supplied to witness generation and `outputs` are the results of the computation.