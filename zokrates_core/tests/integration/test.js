var fs = require("fs");
let Web3 = require('web3');
const solc = require('solc');
const format = process.argv[2]
const abiVersion = process.argv[3];
const CONTRACT_NAME = format + "-" + abiVersion + "-verifier.sol";
const web3 = new Web3(new Web3.providers.HttpProvider('http://localhost:8545'));
console.log(CONTRACT_NAME)

// -----Compile contract-----
const source = fs.readFileSync("target/debug/" + CONTRACT_NAME, 'UTF-8');
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

let jsonInterface = JSON.parse(solc.compile(jsonContractSource));
(async () => {
    const accounts = await web3.eth.getAccounts();
    let abi = jsonInterface.contracts[CONTRACT_NAME]["Verifier"].abi
    let bytecode = jsonInterface.contracts[CONTRACT_NAME]['Verifier'].evm.bytecode

    //There is a solc issue, that for unknown reasons wont link the BN256G2 Library automatically for gm17 v1 and v2 contracts. I dont know why this is happening, 
    //the contracts compile and deploy without any issue on remix. To fix this, the the BN256G2 Library must be compiled and deployed by itself, after that, 
    //the library placeholder must be replaced with the library address in the contracts bytecode
    if (format == "gm17") {
        let library = await deployLibrary();
        //replace lib placeholder with lib address in bytecode
        bytecode.object = bytecode.object.replace(/\_\_\$[a-f0-9]{34}\$\_\_/g, library["_address"].replace("0x", ""))
    }

    let contract = new web3.eth.Contract(abi)
        .deploy({ data: '0x' + bytecode.object })
        .send({
            from: accounts[0],
            gas: '2000000'
        })
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
            process.exit(1);
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
                if (tx.status == true && !correct) {
                    console.log("Verification has been successful with invalid proof data! THIS IS A BUG")
                    process.exit(1)
                }

                if (tx.status == true) {
                    console.log("Correct proof works! Gas used: " + tx.gasUsed)
                }
            })
            .catch(err => {
                if (!correct) {
                    console.log("False proof not verified! Success")
                } else {
                    console.log(err);
                    process.exit(1)
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
                if (tx.status == true && !correct) {
                    console.log("Verification has been successful with invalid proof data! THIS IS A BUG")
                    process.exit(1);
                }

                if (correct && tx.status == true) {
                    console.log("Correct proof works! Gas used: " + tx.gasUsed)
                }
            })
            .catch(err => {
                if (!correct) {
                    console.log("False proof not verified! Success")
                } else {
                    console.log(err);
                    process.exit(1)
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
                if (tx.status == true && !correct) {
                    console.log("Verification has been successful with invalid proof data! THIS IS A BUG")
                    process.exit(1);
                }

                if (tx.status == true) {
                    console.log("Correct proof works! Gas used: " + tx.gasUsed)
                }

            })
            .catch(err => {
                if (!correct) {
                    console.log("False proof not verified! Success")
                } else {
                    console.log(err);
                    process.exit(1)
                }
            })
    }

    function getProof(correct) {
        let json = JSON.parse(fs.readFileSync("target/debug/" + format + "-proof.json"));
        let inputs = json["inputs"];
        let proof = json["proof"]
        //falsifies proof to check if verification fails
        if (!correct) {
            proof["a"][0] = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        }
        if (abiVersion == "v1") {
            return [Object.values(proof), Object.values(inputs)];
        } else if (abiVersion == "v2") {
            return [proof, inputs]
        }
    }

    //function used for deploying BN256G2 Library, used for gm17 only
    function deployLibrary() {
        let jsonContractSourceBin = JSON.stringify({
            language: 'Solidity',
            sources: {
                ["BN256G2"]: {
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
        let jsonInterfaceBin = JSON.parse(solc.compile(jsonContractSourceBin));
        let abiLib = jsonInterfaceBin.contracts["BN256G2"]["BN256G2"].abi
        let bytecodeLib = jsonInterfaceBin.contracts["BN256G2"]['BN256G2'].evm.bytecode
        return new web3.eth.Contract(abiLib)
            .deploy({ data: '0x' + bytecodeLib.object })
            .send({
                from: accounts[0],
                gas: '2000000'
            })
            .on('receipt', (tx) => {
                if (tx.status == false) {
                    console.log("Library couldn't be deployed");
                    process.exit(1);
                }
            })
    }
})();
