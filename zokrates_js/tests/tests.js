const assert = require('assert');
const { initialize } = require('../node/index.js');

describe('tests', function() {

    // initialize once before running tests
    before(function (done) {
        initialize().then(zokrates => {
            this.zokrates = zokrates;
            done();
        });
    });

    describe("compilation", () => {
        it('should compile', function() {
            assert.doesNotThrow(() => {
                const artifacts = this.zokrates.compile("def main() -> field: return 42");
                assert.ok(artifacts !== undefined);
            })
        });

        it('should throw on invalid code', function() {
            assert.throws(() => this.zokrates.compile(":-)"));
        });

        it('should resolve stdlib module', function() {
            const stdlib = require('../stdlib.json');
            assert.doesNotThrow(() => {
                const code = `import "${Object.keys(stdlib)[0]}" as func\ndef main(): return`;
                this.zokrates.compile(code);
            });
        });

        it('should resolve user module', function() {
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
                this.zokrates.compile(code, options);
            });
        });

        it('should throw on unresolved module', function() {
            assert.throws(() => {
                const code = 'import "test" as test\ndef main() -> field: return test()';
                this.zokrates.compile(code);
            });
        });
    });

    describe("computation", () => {
        it('should compute with valid inputs', function() {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);

                const result = this.zokrates.computeWitness(artifacts, ["2"]);
                const output = JSON.parse(result.output);

                assert.deepEqual(output, ["4"]);
            });
        });

        it('should throw on invalid input count', function() {
            assert.throws(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);

                this.zokrates.computeWitness(artifacts, ["1", "2"]);
            });
        });

        it('should throw on invalid input type', function() {
            assert.throws(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);

                this.zokrates.computeWitness(artifacts, [true]);
            });
        });
    });

    describe("setup", () => {
        it('should run setup', function() {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);

                this.zokrates.setup(artifacts.program);
            });
        });
    });

    describe("export-verifier", () => {
        it('should export solidity verifier', function() {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);
                const keypair = this.zokrates.setup(artifacts.program);

                const verifier = this.zokrates.exportSolidityVerifier(keypair.vk, "v1");
                assert.ok(verifier.length > 0);
            });
        });
    });

    describe("generate-proof", () => {
        it('should generate proof', function() {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);
                const computationResult = this.zokrates.computeWitness(artifacts, ["2"])
                const keypair = this.zokrates.setup(artifacts.program);
                const proof = this.zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk);

                assert.ok(proof !== undefined);
                assert.deepEqual(proof.inputs, ["0x0000000000000000000000000000000000000000000000000000000000000004"]);
            })
        });
    });

    describe("verify", () => {
        it('should pass', function() {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);
                const computationResult = this.zokrates.computeWitness(artifacts, ["2"])
                const keypair = this.zokrates.setup(artifacts.program);
                const proof = this.zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk);

                assert(this.zokrates.verify(keypair.vk, proof) == true);
            })
        });

        it('should fail', function() {
            assert.doesNotThrow(() => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = this.zokrates.compile(code);
                const computationResult = this.zokrates.computeWitness(artifacts, ["2"])
                const keypair = this.zokrates.setup(artifacts.program);
                let proof = this.zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk);

                // falsify proof
                proof["proof"]["a"][0] = "0x0000000000000000000000000000000000000000000000000000000000000000";
                assert(this.zokrates.verify(keypair.vk, proof) == false);
            })
        });
    });
});