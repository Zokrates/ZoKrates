const assert = require('assert');
const { initialize } = require('../node/index.js');

describe('tests', function() {
    let zokrates;

    // initialize once before running tests
    before((done) => {
        initialize().then((provider) => {
            zokrates = provider;
            done();
        });
    });

    describe("compilation", () => {
        it('should compile', () => {
            assert.doesNotThrow(() => {
                const artifacts = zokrates.compile("def main() -> field: return 42");
                assert.ok(artifacts !== undefined);
            })
        });

        it('should throw on invalid code', () => {
            assert.throws(() => zokrates.compile(":-)"));
        });

        it('should resolve stdlib module', () => {
            const stdlib = require('../stdlib.json');
            assert.doesNotThrow(() => {
                const code = `import "${Object.keys(stdlib)[0]}" as func\ndef main(): return`;
                zokrates.compile(code);
            });
        });

        it('should resolve user module', () => {
            assert.doesNotThrow(() => {
                const code = 'import "test" as test\ndef main() -> field: return test()';
                const options = {
                    resolveCallback: (_, path) => {
                        return {
                            source: "def main() -> (field): return 1",
                            location: path
                        }
                    }
                };
                zokrates.compile(code, options);
            });
        });

        it('should throw on unresolved module', () => {
            assert.throws(() => {
                const code = 'import "test" as test\ndef main() -> field: return test()';
                zokrates.compile(code);
            });
        });
    });

    describe("computation", () => {
        it('should compute with valid inputs', () => {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = zokrates.compile(code);

                const result = zokrates.computeWitness(artifacts, ["2"]);
                const output = JSON.parse(result.output);
                assert.deepEqual(output, ["4"]);
            });
        });

        it('should throw on invalid input count', () => {
            assert.throws(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = zokrates.compile(code);
                zokrates.computeWitness(artifacts, ["1", "2"]);
            });
        });

        it('should throw on invalid input type', () => {
            assert.throws(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = zokrates.compile(code);
                zokrates.computeWitness(artifacts, [true]);
            });
        });
    });

    describe("bellman", () => {
        describe("groth16", () => {
            const options = { 
                backend: "bellman", 
                curve: "bn128", 
                scheme: "g16" 
            };

            let artifacts;
            let computationResult;
            let keypair;
            let proof;

            before((done) => {
                const code = 'def main(private field a) -> field: return a * a';
                artifacts = zokrates.compile(code);
                computationResult = zokrates.computeWitness(artifacts, ["2"]);
                done();
            });

            it("setup", () => {
                assert.doesNotThrow(() => {
                    keypair = zokrates.setup(artifacts.program, options);
                });
            });

            it("generate proof", () => {
                assert.doesNotThrow(() => {
                    proof = zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk, options);
                    assert.ok(proof !== undefined);
                    assert.deepEqual(proof.inputs, ["0x0000000000000000000000000000000000000000000000000000000000000004"]);
                });
            });

            it("export solidity verifier", () => {
                let verifier = zokrates.exportSolidityVerifier(keypair.vk, options);
                assert(verifier.length > 0);
            });

            it("verify with valid proof", () => {
                assert.doesNotThrow(() => {
                    assert(zokrates.verify(keypair.vk, proof, options) === true);
                });
            });

            it("verify with invalid proof", () => {
                // falsify proof
                proof["proof"]["a"][0] = "0x0000000000000000000000000000000000000000000000000000000000000000";
                assert(zokrates.verify(keypair.vk, proof, options) === false);
            });
        });
    });

    describe("ark", () => {
        describe("gm17", () => {
            const options = { 
                backend: "ark", 
                curve: "bn128", 
                scheme: "gm17" 
            };

            let artifacts;
            let computationResult;
            let keypair;
            let proof;

            before((done) => {
                const code = 'def main(private field a) -> field: return a * a';
                artifacts = zokrates.compile(code);
                computationResult = zokrates.computeWitness(artifacts, ["2"]);
                done();
            });

            it("setup", () => {
                assert.doesNotThrow(() => {
                    keypair = zokrates.setup(artifacts.program, options);
                });
            });

            it("generate proof", () => {
                assert.doesNotThrow(() => {
                    proof = zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk, options);
                    assert.ok(proof !== undefined);
                    assert.deepEqual(proof.inputs, ["0x0000000000000000000000000000000000000000000000000000000000000004"]);
                });
            });

            it("verify with valid proof", () => {
                assert.doesNotThrow(() => {
                    assert(zokrates.verify(keypair.vk, proof, options) === true);
                });
            });

            it("verify with invalid proof", () => {
                // falsify proof
                proof["proof"]["a"][0] = "0x0000000000000000000000000000000000000000000000000000000000000000";
                assert(zokrates.verify(keypair.vk, proof, options) === false);
            });
        });

        describe("marlin", () => {
            const options = { 
                backend: "ark", 
                curve: "bn128", 
                scheme: "marlin" 
            };

            let artifacts;
            let computationResult;
            let keypair;
            let proof;

            before((done) => {
                const code = 'def main(private field a, private field b) -> bool: return a * a == b';
                artifacts = zokrates.compile(code);
                computationResult = zokrates.computeWitness(artifacts, ["2", "4"]);
                done();
            });

            it("setup", () => {
                assert.doesNotThrow(() => {
                    const srs = zokrates.universalSetup("bn128", 4);
                    keypair = zokrates.setupWithSrs(srs, artifacts.program, options);
                });
            });

            it("generate proof", () => {
                assert.doesNotThrow(() => {
                    proof = zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk, options);
                    assert.ok(proof !== undefined);
                    assert.deepEqual(proof.inputs, ["0x0000000000000000000000000000000000000000000000000000000000000001"]);
                });
            });

            it("verify with valid proof", () => {
                assert.doesNotThrow(() => {
                    assert(zokrates.verify(keypair.vk, proof, options) === true);
                });
            });

            it("verify with invalid proof", () => {
                // falsify proof
                proof["inputs"][0] = "0x0000000000000000000000000000000000000000000000000000000000000000";
                assert(zokrates.verify(keypair.vk, proof, options) === false);
            });
        });
    });
});