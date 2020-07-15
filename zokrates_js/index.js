import wrapper from './wrapper';
import stdlib from './stdlib.json';

const initialize = async () => {
  const zokrates = await import('./pkg/index.js');
  return wrapper({ zokrates, stdlib });
}

export { initialize };