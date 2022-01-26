const assert = require("assert");
const { initialize } = require("../node/index.js");

describe("tests", function () {
  let zokrates;

  // initialize once before running tests
  before((done) => {
    initialize().then((provider) => {
      zokrates = provider;
      done();
    });
  });

  describe("compilation", () => {
    it("should compile", () => {
      assert.doesNotThrow(() => {
        const artifacts = zokrates.compile("def main() -> field: return 42");
        assert.ok(artifacts !== undefined);
      });
    });

    it("should throw on invalid code", () => {
      assert.throws(() => zokrates.compile(":-)"));
    });

    it("should resolve stdlib module", () => {
      const stdlib = require("../stdlib.json");
      assert.doesNotThrow(() => {
        const code = `import "${
          Object.keys(stdlib)[0]
        }" as func\ndef main(): return`;
        zokrates.compile(code);
      });
    });

    it("should resolve user module", () => {
      assert.doesNotThrow(() => {
        const code =
          'import "test" as test\ndef main() -> field: return test()';
        const options = {
          resolveCallback: (_, path) => {
            return {
              source: "def main() -> (field): return 1",
              location: path,
            };
          },
        };
        zokrates.compile(code, options);
      });
    });

    it("should throw on unresolved module", () => {
      assert.throws(() => {
        const code =
          'import "test" as test\ndef main() -> field: return test()';
        zokrates.compile(code);
      });
    });
  });

  describe("computation", () => {
    it("should compute with valid inputs", () => {
      assert.doesNotThrow(() => {
        const code = "def main(private field a) -> field: return a * a";
        const artifacts = zokrates.compile(code);

        const result = zokrates.computeWitness(artifacts, ["2"]);
        const output = JSON.parse(result.output);
        assert.deepEqual(output, ["4"]);
      });
    });

    it("should throw on invalid input count", () => {
      assert.throws(() => {
        const code = "def main(private field a) -> field: return a * a";
        const artifacts = zokrates.compile(code);
        zokrates.computeWitness(artifacts, ["1", "2"]);
      });
    });

    it("should throw on invalid input type", () => {
      assert.throws(() => {
        const code = "def main(private field a) -> field: return a * a";
        const artifacts = zokrates.compile(code);
        zokrates.computeWitness(artifacts, [true]);
      });
    });
  });

  const runWithOptions = (options) => {
    let artifacts;
    let computationResult;
    let keypair;
    let proof;

    before((done) => {
      const code = "def main(private field a) -> field: return a + a";
      artifacts = zokrates.compile(code, { curve: options.curve });
      computationResult = zokrates.computeWitness(artifacts, ["2"]);
      done();
    });

    it("setup", () => {
      assert.doesNotThrow(() => {
        if (options.scheme === "marlin") {
          const srs = zokrates.universalSetup(options.curve, 2);
          keypair = zokrates.setupWithSrs(srs, artifacts.program, options);
        } else {
          keypair = zokrates.setup(artifacts.program, options);
        }
      });
    });

    it("generate proof", () => {
      assert.doesNotThrow(() => {
        proof = zokrates.generateProof(
          artifacts.program,
          computationResult.witness,
          keypair.pk,
          options
        );
        assert.ok(proof !== undefined);
        assert.ok(proof.proof.hasOwnProperty("a"));
        assert.ok(proof.proof.hasOwnProperty("b"));
        assert.ok(proof.proof.hasOwnProperty("c"));
        assert.equal(proof.inputs.length, 1);
      });
    });

    it("verify with valid proof", () => {
      assert.doesNotThrow(() => {
        assert(zokrates.verify(keypair.vk, proof, options) === true);
      });
    });

    it("falsify proof", () => {
      let tmp = proof["proof"]["a"][0];
      proof["proof"]["a"][0] = proof["proof"]["a"][1];
      proof["proof"]["a"][1] = tmp;
      assert(zokrates.verify(keypair.vk, proof, options) === false);
    });
  };

  describe("bellman", () => {
    describe("groth16", () => {
      for (const curve of ["bn128", "bls12_381"]) {
        describe(curve, () =>
          runWithOptions({ backend: "bellman", scheme: "g16", curve })
        );
      }
    });
  });

  describe("ark", () => {
    for (const scheme of ["gm17", "marlin"]) {
      describe(scheme, () => {
        for (const curve of ["bn128", "bls12_377", "bw6_761"]) {
          describe(curve, () =>
            runWithOptions({ backend: "ark", scheme: "gm17", curve })
          );
        }
      });
    }
  });
});
