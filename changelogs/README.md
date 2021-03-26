## Adding a changelog

Pull request authors are expected to include a changelog file explaining the changes introduced by the pull request. 
The changelog file should be a new file created in the `changelogs/unreleased` folder. 
The file should follow the naming convention of `pr-username` and the contents of the file 
should be your text for the changelog.

### Example
```
changelogs/unreleased   # folder to place changelogs
    101-username        # your changelog file (pull request #101 by @username)
```

Any user-facing change must have a changelog entry. If a pull request does not warrant a changelog, the CI check for a changelog can be skipped by applying a `changelog-not-required` label.
