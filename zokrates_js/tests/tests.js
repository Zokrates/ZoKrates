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
    let provider;
    let artifacts;
    let computationResult;
    let keypair;
    let proof;

    before((done) => {
      provider = zokrates.withOptions(options);
      done();
    });

    it("compile", () => {
      assert.doesNotThrow(() => {
        const code =
          "def main(private field a, field b) -> bool: return a * a == b";
        artifacts = provider.compile(code);
      });
    });

    it("compute witness", () => {
      assert.doesNotThrow(() => {
        computationResult = provider.computeWitness(artifacts, ["2", "4"]);
      });
    });

    it("setup", () => {
      assert.doesNotThrow(() => {
        if (options.scheme === "marlin") {
          const srs = provider.universalSetup(4);
          keypair = provider.setupWithSrs(srs, artifacts.program);
        } else {
          keypair = provider.setup(artifacts.program);
        }
      });
    });

    if (options.curve === "bn128" && ["g16", "gm17"].includes(options.scheme)) {
      it("export verifier", () => {
        assert.doesNotThrow(() => {
          let verifier = provider.exportSolidityVerifier(keypair.vk);
          assert.ok(verifier.includes("contract"));
        });
      });
    }

    it("generate proof", () => {
      assert.doesNotThrow(() => {
        proof = provider.generateProof(
          artifacts.program,
          computationResult.witness,
          keypair.pk
        );
        assert.ok(proof !== undefined);
        assert.equal(proof.inputs.length, 2);
      });
    });

    it("verify", () => {
      assert.doesNotThrow(() => {
        assert(provider.verify(keypair.vk, proof) === true);
      });
    });
  };

  for (const scheme of ["g16", "gm17", "marlin"]) {
    describe(scheme, () => {
      for (const curve of ["bn128", "bls12_381", "bls12_377", "bw6_761"]) {
        describe(curve, () => runWithOptions({ scheme, curve }));
      }
    });
  }
});
