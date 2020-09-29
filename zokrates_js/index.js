import wrapper from './wrapper.js';
import stdlib from './stdlib.json';
import metadata from './metadata.json';

const initialize = async () => {
  const zokrates = await import('./pkg/index.js');
  return wrapper({ zokrates, stdlib });
}

export { initialize, metadata };