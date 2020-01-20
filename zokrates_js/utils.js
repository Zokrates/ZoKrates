export function getAbsolutePath(basePath, relativePath) {
  if (relativePath[0] !== '.') {
      return relativePath;
  }
  var stack = basePath.split('/');
  var chunks = relativePath.split('/');
  stack.pop();

  for(var i = 0; i < chunks.length; i++) {
      if (chunks[i] == '.') {
          continue;
      } else if (chunks[i] == '..') {
          stack.pop();
      } else {
          stack.push(chunks[i]);
      }
  }
  return stack.join('/');
}

export function appendExtension(path, extension) {
  if (path.endsWith(extension)) {
      return path;
  }
  return path.concat(extension);
}