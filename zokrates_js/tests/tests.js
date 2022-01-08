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
        it('should compile', async function() {
            let result = await this.zokrates.compile("def main() -> field: return 42");
            assert.ok(result !== undefined);
        });

        it('should throw on invalid code', async function() {
            return assert.rejects(() => this.zokrates.compile(":-)"));
        });

        it('should resolve stdlib module', async function() {
            const stdlib = require('../stdlib.json');
            const code = `import "${Object.keys(stdlib)[0]}" as func\ndef main(): return`;
            return this.zokrates.compile(code);
        });

        it('should resolve user module', async function() {
            const code = 'import "test" as test\ndef main() -> field: return test()';
            const options = {
                resolveCallback: (_, path) => {
                    return {
                        source: "def main() -> (field): return 1",
                        location: path
                    }
                }
            };
            return this.zokrates.compile(code, options);
        });

        it('should throw on unresolved module', async function() {
            return assert.rejects(() => {
                const code = 'import "test" as test\ndef main() -> field: return test()';
                return this.zokrates.compile(code);
            });
        });
    });

    describe("computation", () => {
        it('should compute with valid inputs', async function() {
            const code = 'def main(private field a) -> field: return a * a';
            const artifacts = await this.zokrates.compile(code);

            const result = await this.zokrates.computeWitness(artifacts, ["2"]);
            const output = JSON.parse(result.output);
            assert.deepEqual(output, ["4"]);
        });

        it('should throw on invalid input count', async function() {
            return assert.rejects(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);
    
                return this.zokrates.computeWitness(artifacts, ["1", "2"]);
            });
        });

        it('should throw on invalid input type', async function() {
            return assert.rejects(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);
    
                return this.zokrates.computeWitness(artifacts, [true]);
            });
        });
    });

    describe("setup", () => {
        it('should run setup', async function() {
            return assert.doesNotReject(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);

                return this.zokrates.setup(artifacts.program);
            });
        });
    });

    describe("export-verifier", () => {
        it('should export solidity verifier', async function() {
            return assert.doesNotReject(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);
                const keypair = await this.zokrates.setup(artifacts.program);

                const verifier = await this.zokrates.exportSolidityVerifier(keypair.vk);
                assert.ok(verifier.length > 0);
            });
        });
    });

    describe("generate-proof", () => {
        it('should generate proof', async function() {
            return assert.doesNotReject(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);
                const computationResult = await this.zokrates.computeWitness(artifacts, ["2"])
                const keypair = await this.zokrates.setup(artifacts.program);
                const proof = await this.zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk);

                assert.ok(proof !== undefined);
                assert.deepEqual(proof.inputs, ["0x0000000000000000000000000000000000000000000000000000000000000004"]);
            })
        });
    });

    describe("verify", () => {
        it('should pass', async function() {
            return assert.doesNotReject(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);
                const computationResult = await this.zokrates.computeWitness(artifacts, ["2"])
                const keypair = await this.zokrates.setup(artifacts.program);
                const proof = await this.zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk);

                assert(await this.zokrates.verify(keypair.vk, proof) == true);
            })
        });

        it('should fail', async function() {
            return assert.doesNotReject(async () => {
                const code = 'def main(private field a) -> field: return a * a';
                const artifacts = await this.zokrates.compile(code);
                const computationResult = await this.zokrates.computeWitness(artifacts, ["2"])
                const keypair = await this.zokrates.setup(artifacts.program);
                let proof = await this.zokrates.generateProof(artifacts.program, computationResult.witness, keypair.pk);

                // falsify proof
                proof["proof"]["a"][0] = "0x0000000000000000000000000000000000000000000000000000000000000000";
                assert(await this.zokrates.verify(keypair.vk, proof) == false);
            })
        });
    });
});