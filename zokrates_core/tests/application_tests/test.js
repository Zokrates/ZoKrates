var fs = require("fs");
let Web3 = require('web3');
const web3 = new Web3(new Web3.providers.HttpProvider('http://localhost:8545'));
const solc = require('solc');
const format = process.argv[2]
const abiVersion = process.argv[3];
const CONTRACT_NAME = format + "-" + abiVersion + "-verifier.sol";

console.log(CONTRACT_NAME)

// -----Compile contract-----
const source = fs.readFileSync("target/release/" + CONTRACT_NAME, 'UTF-8');
let jsonContractSource = JSON.stringify({
    language: 'Solidity',
    sources: {
        [CONTRACT_NAME]: {
            content: source,
        },
    },
    settings: {
        outputSelection: {
            '*': {
                '*': ['abi', "evm.bytecode"],
            },
        },
    },
});

const jsonInterface = JSON.parse(solc.compile(jsonContractSource));
// -----Depoly Contract-----
let abi = jsonInterface.contracts[CONTRACT_NAME]["Verifier"].abi
let bytecode = jsonInterface.contracts[CONTRACT_NAME]['Verifier'].evm.bytecode
let contract = new web3.eth.Contract(abi)
let deployTx = contract.deploy({ data: '0x' + bytecode.object });
web3.eth.accounts.create();
web3.eth.getAccounts().then(accounts => {
    deployTx.send({ from: accounts[0], gas: 5000000 })
        .on('receipt', (tx) => {
            if (tx.status == true) {
                console.log("Contract Depolyed! Gas used: " + tx.gasUsed)
            }
        })
        .then(newContractInstance => {
            contract = newContractInstance;
            makeTransaction(accounts[0], true)
                .then(() => {
                    makeTransaction(accounts[0], false);
                })
        })
        .catch(err => {
            console.log(err);
        })
})

function makeTransaction(account, correct) {
    let parameters = getProof();
    if (abiVersion == "v1") {
        if (format == "g16" || format == "gm17") {
            return verifyTxG16_GM17_ABIV1(account, correct);
        } else if (format == "pghr13") {
            return verifyTxPGHR13_ABIV1(account, correct);
        }
    } else {
        return verifyTxABIV2(account, correct);
    }
}

function verifyTxABIV2(account, correct) {
    let parameters = getProof(correct);
    return contract.methods.verifyTx(parameters[0], parameters[1]).send({ from: account, gas: 5000000 })
        .on('receipt', (tx) => {
            if (tx.status == true) {
                console.log("Correct proof works! Gas used: " + tx.gasUsed)
            }
        })
        .catch(err => {
            if (!correct) {
                console.log("False proof not verified! Success")
            } else {
                console.log(err);
            }
        })
}

function verifyTxG16_GM17_ABIV1(account, correct) {
    let parameters = getProof(correct);
    return contract.methods.verifyTx(
        parameters[0][0],
        parameters[0][1],
        parameters[0][2],
        parameters[1]
    ).send({ from: account, gas: 5000000 })
        .on('receipt', (tx) => {
            if (correct && tx.status == true) {
                console.log("Correct proof works! Gas used: " + tx.gasUsed)
            }
        })
        .catch(err => {
            if (!correct) {
                console.log("False proof not verified! Success")
            } else {
                console.log(err);
            }
        })
}

function verifyTxPGHR13_ABIV1(account, correct) {
    let parameters = getProof(correct);
    return contract.methods.verifyTx(
        parameters[0][0],
        parameters[0][1],
        parameters[0][2],
        parameters[0][3],
        parameters[0][4],
        parameters[0][5],
        parameters[0][6],
        parameters[0][7],
        parameters[1]
    ).send({ from: account, gas: 5000000 })
        .on('receipt', (tx) => {
            if (tx.status == true) {
                console.log("Correct proof works! Gas used: " + tx.gasUsed)
            } else if (!correct && tx.status == false) {
                console.log("False proof didn't work! Gas used: " + tx.gasUsed)
            }
        })
        .catch(err => {
            if (!correct) {
                console.log("False proof not verified! Success")
            } else {
                console.log(err);
            }
        })
}

function getProof(correct) {
    let json = JSON.parse(fs.readFileSync("target/release/" + format + "-proof.json"));
    let inputs = json["inputs"];
    let proof = json["proof"]
    //falsifies proof to check if verification fails
    if (!correct) {
        proof["A"][0] = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    }
    if (abiVersion == "v1") {
        return [Object.values(proof), Object.values(inputs)];
    } else if (abiVersion == "v2") {
        return [proof, inputs]
    }
}
