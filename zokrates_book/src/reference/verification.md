# Verification

Passed to the verifier contract, a proof can be checked.
For example, using `web3`, a call would look like the following:

```javascript
const accounts = await web3.eth.getAccounts();
const address = '0x456...'; // verifier contract address

let verifier = new web3.eth.Contract(abi, address, {
    from: accounts[0], // default from address
    gasPrice: '20000000000000'; // default gas price in wei
});

let result = await verifier.methods
    .verifyTx(proof.proof, proof.inputs)
    .call({ from: accounts[0] });
```