export interface ResolverResult {
  source: string,
  location: string
}

export interface SetupKeypair {
  vk: string,
  pk: Uint8Array,
}

export function initialize(callback: (location: string, path: string) => ResolverResult): Promise<void>;
export function compile(source: string, location: string): Uint8Array;
export function getStdLib(): object;
export function computeWitness(program: Uint8Array, args: string[]): string;
export function setup(program: Uint8Array): SetupKeypair;
export function exportSolidityVerifier(verifyingKey: string, isAbiv2: boolean): string;
export function generateProof(program: Uint8Array, witness: string, provingKey: Uint8Array): string;