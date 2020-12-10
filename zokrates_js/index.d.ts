declare module 'zokrates-js' {

  export type Fq = string;
  export type Fq2 = [Fq, Fq];

  export type G1Affine = [Fq, Fq];
  export type G2Affine = [Fq2, Fq2];
  export type ProvingKey = Uint8Array;

  export type SolidityAbi = "v1" | "v2";
  export type ResolveCallback = (location: string, path: string) => ResolverResult;

   export interface CompileConfig {
      allow_unconstrained_variables?: boolean
   }

  export interface CompileOptions {
    location?: string,
    resolveCallback?: ResolveCallback,
    config?: CompileConfig
  }

  export interface VerificationKey {
    alpha: G1Affine,
    beta: G2Affine,
    gamma: G2Affine,
    delta: G2Affine,
    gamma_abc: G1Affine[]
  }

  export interface ProofPoints {
    a: G1Affine,
    b: G2Affine,
    c: G1Affine
  }

  export interface Proof {
    proof: ProofPoints,
    inputs: string[]
  }

  export interface ResolverResult {
    source: string,
    location: string
  }

  export interface ComputationResult {
    witness: string,
    output: string
  }

  export interface CompilationArtifacts {
    program: Uint8Array,
    abi: string,
  }
  
  export interface SetupKeypair {
    vk: VerificationKey,
    pk: ProvingKey,
  }

  export interface ZoKratesProvider {
    compile(source: string, options?: CompileOptions): CompilationArtifacts;
    setup(program: Uint8Array): SetupKeypair;
    computeWitness(artifacts: CompilationArtifacts, args: any[]): ComputationResult;
    exportSolidityVerifier(verificationKey: VerificationKey, abi: SolidityAbi): string;
    generateProof(program: Uint8Array, witness: string, provingKey: Uint8Array): Proof;
    verify(verificationKey: VerificationKey, proof: Proof): boolean;
  }

  export interface Metadata {
    version: string
  }

  export function initialize(): Promise<ZoKratesProvider>;
  export var metadata: Metadata;
}
