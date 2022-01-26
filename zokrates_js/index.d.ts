declare module "zokrates-js" {
  export type Curve = "bn128" | "bls12_381" | "bls12_377" | "bw6_761";
  export type Backend = "bellman" | "ark";
  export type Scheme = "g16" | "gm17" | "marlin";

  export type Fq = string;
  export type Fq2 = [Fq, Fq];

  export type G1Affine = [Fq, Fq];
  export type G2Affine = [Fq2, Fq2];
  export type ProvingKey = Uint8Array;

  export type ResolveCallback = (
    location: string,
    path: string
  ) => ResolverResult;

  export interface CompileConfig {
    allow_unconstrained_variables?: boolean;
    isolate_branches?: boolean;
  }

  export interface CompileOptions {
    location?: string;
    resolveCallback?: ResolveCallback;
    config?: CompileConfig;
  }

  export interface VerificationKey {
    alpha: G1Affine;
    beta: G2Affine;
    gamma: G2Affine;
    delta: G2Affine;
    gamma_abc: G1Affine[];
  }

  export interface ProofPoints {
    a: G1Affine;
    b: G2Affine;
    c: G1Affine;
  }

  export interface Proof {
    proof: ProofPoints;
    inputs: string[];
  }

  export interface ResolverResult {
    source: string;
    location: string;
  }

  export interface ComputationResult {
    witness: string;
    output: string;
  }

  export interface CompilationArtifacts {
    program: Uint8Array;
    abi: string;
  }

  export interface SetupKeypair {
    vk: VerificationKey;
    pk: ProvingKey;
  }

  export type Options = {
    curve: Scheme;
    backend: Backend;
    scheme: Curve;
  };

  type AtLeast<T, K extends keyof T> = Partial<T> & Pick<T, K>;

  export type SpecializedZoKratesProvider = {
    compile(
      source: string,
      compileOptions?: CompileOptions
    ): CompilationArtifacts;
    computeWitness(
      artifacts: CompilationArtifacts,
      args: any[]
    ): ComputationResult;
    setup(program: Uint8Array): SetupKeypair;
    universalSetup(size: number): Uint8Array;
    setupWithSrs(srs: Uint8Array, program: Uint8Array): SetupKeypair;
    generateProof(
      program: Uint8Array,
      witness: string,
      provingKey: Uint8Array
    ): Proof;
    verify(verificationKey: VerificationKey, proof: Proof): boolean;
    exportSolidityVerifier(verificationKey: VerificationKey): string;
  };

  export interface ZoKratesProvider {
    withOptions(options: Options): SpecializedZoKratesProvider;
    compile(
      source: string,
      compileOptions?: CompileOptions
    ): CompilationArtifacts;
    computeWitness(
      artifacts: CompilationArtifacts,
      args: any[]
    ): ComputationResult;
    setup(
      program: Uint8Array,
      options: AtLeast<Options, "backend" | "scheme">
    ): SetupKeypair;
    universalSetup(curve: Curve, size: number): Uint8Array;
    setupWithSrs(
      srs: Uint8Array,
      program: Uint8Array,
      options: AtLeast<Options, "backend" | "scheme">
    ): SetupKeypair;
    generateProof(
      program: Uint8Array,
      witness: string,
      provingKey: Uint8Array,
      options: AtLeast<Options, "backend" | "scheme">
    ): Proof;
    verify(
      verificationKey: VerificationKey,
      proof: Proof,
      options: Options
    ): boolean;
    exportSolidityVerifier(
      verificationKey: VerificationKey,
      options: AtLeast<Options, "curve" | "scheme">
    ): string;
  }

  export interface Metadata {
    version: string;
  }

  export function initialize(): Promise<ZoKratesProvider>;
  export var metadata: Metadata;
}
