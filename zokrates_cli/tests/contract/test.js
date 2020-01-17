var fs = require("fs");
let Web3 = require('web3');
const solc = require('solc');
const contractPath = process.argv[2]
const proofPath = process.argv[3]
const format = process.argv[4]
const abiVersion = process.argv[5];
const web3 = new Web3(new Web3.providers.HttpProvider('http://localhost:8545'));

// -----Compile contract-----
const source = fs.readFileSync(contractPath, 'UTF-8');
let jsonContractSource = JSON.stringify({
    language: 'Solidity',
    sources: {
        [contractPath]: {
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
    let abi = jsonInterface.contracts[contractPath]["Verifier"].abi
    let bytecode = jsonInterface.contracts[contractPath]["Verifier"].evm.bytecode

    //There is a solc issue, that for unknown reasons wont link the BN256G2 Library automatically for gm17 v1 and v2 contracts. I dont know why this is happening,
    //the contracts compile and deploy without any issue on remix. To fix this, the the BN256G2 Library must be compiled and deployed by itself, after that,
    //the library placeholder must be replaced with the library address in the contracts bytecode
    if (format == "gm17") {
        let library = await deployLibrary();
        //replace lib placeholder with lib address in bytecode
        bytecode.object = bytecode.object.replace(/\_\_\$[a-f0-9]{34}\$\_\_/g, library["_address"].replace("0x", ""))
    }

    let contract = new web3.eth.Contract(abi)
        .deploy({
            data: '0x' + bytecode.object
        })
        .send({
            from: accounts[0],
            gas: '2000000'
        })
        .on('receipt', (tx) => {
            if (tx.status == true) {
                console.log("Contract Deployed! Gas used: " + tx.gasUsed)
            }
        })
        .then(newContractInstance => {
            contract = newContractInstance;
            Promise.all([makeTransaction(accounts[0], true), makeTransaction(accounts[0], false)])
        })
        .catch(err => {
            console.log(err);
            process.exit(1);
        })

    function makeTransaction(account, correct) {
        let proof = getProof(correct);

        function handleReceipt(tx) {
            if (tx.status == true && !correct) {
                console.log("Verification has been successful with invalid proof data! THIS IS A BUG")
                process.exit(1)
            }

            if (tx.status == true) {
                console.log("Correct proof works! Gas used: " + tx.gasUsed)
            }
        }

        function handleError(err, correct) {
            if (!correct) {
                console.log("False proof not verified! Success")
            } else {
                console.log(err);
                process.exit(1)
            }
        }

        if (abiVersion == "v1") {
            if (format == "g16" || format == "gm17") {
                return verifyTxG16_GM17_ABIV1(proof, account, correct).on('receipt', handleReceipt)
                    .catch(handleError);
            } else if (format == "pghr13") {
                return verifyTxPGHR13_ABIV1(proof, account, correct).on('receipt', handleReceipt)
                    .catch(handleError);
            }
        } else {
            return verifyTxABIV2(proof, account, correct).on('receipt', handleReceipt)
                .catch(handleError);
        }
    }

    function verifyTxABIV2(proof, account, correct) {
        contract.methods.verifyTx(proof[0], proof[1]).send({
            from: account,
            gas: 5000000
        })
    }

    function verifyTxG16_GM17_ABIV1(proof, account, correct) {
        return contract.methods.verifyTx(
            proof[0][0],
            proof[0][1],
            proof[0][2],
            proof[1]
        ).send({
            from: account,
            gas: 5000000
        })
    }

    function verifyTxPGHR13_ABIV1(proof, account, correct) {
        return contract.methods.verifyTx(
            proof[0][0],
            proof[0][1],
            proof[0][2],
            proof[0][3],
            proof[0][4],
            proof[0][5],
            proof[0][6],
            proof[0][7],
            proof[1]
        ).send({
            from: account,
            gas: 5000000
        })
    }

    function getProof(correct) {
        let json = JSON.parse(fs.readFileSync(proofPath));
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
            .deploy({
                data: '0x' + bytecodeLib.object
            })
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