# Verification

Passed to the verifier contract, a given proof can be checked.
For example, using `web3`, a call would look like the following:

```javascript
const accounts = await web3.eth.getAccounts();
const address = '0x456...'; // verifier contract address

let verifier = new web3.eth.Contract(abi, address, {
    from: accounts[0], // default from address
    gasPrice: '20000000000000'; // default gas price in wei
});

verifier.methods.verifyTx(proof.proof, proof.inputs)
    .send({
        from: accounts[0], // default from address
        gas: 5000000 // gas limit
    });
```