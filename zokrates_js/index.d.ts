declare module 'zokrates-js' {

  export type Fq = string;
  export type Fq2 = [Fq, Fq];

  export type G1Affine = [Fq, Fq];
  export type G2Affine = [Fq2, Fq2];
  export type ProvingKey = Uint8Array;

  export type ResolveCallback = (location: string, path: string) => ResolverResult;

   export interface CompileConfig {
      isolate_branches?: boolean
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

  export interface Abi {
    inputs: Array<any>,
    outputs: Array<any>
  }

  export interface CompilationArtifacts {
    program: Uint8Array,
    abi: Abi,
  }
  
  export interface SetupKeypair {
    vk: VerificationKey,
    pk: ProvingKey,
  }

  export interface ZoKratesProvider {
    compile(source: string, options?: CompileOptions): Promise<CompilationArtifacts>;
    setup(program: Uint8Array): Promise<SetupKeypair>;
    computeWitness(artifacts: CompilationArtifacts, args: any[]): Promise<ComputationResult>;
    exportSolidityVerifier(verificationKey: VerificationKey): Promise<string>;
    generateProof(program: Uint8Array, witness: string, provingKey: Uint8Array): Promise<Proof>;
    verify(verificationKey: VerificationKey, proof: Proof): Promise<boolean>;
  }

  export interface Metadata {
    version: string
  }

  export function initialize(): Promise<ZoKratesProvider>;
  export var metadata: Metadata;
}
