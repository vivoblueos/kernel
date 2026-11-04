# Submit pull requests

## New work

Fork [vivoblueos/blueos](https://github.com/vivoblueos/blueos) and submit a PR
using the usual GitHub workflow.

## Existing component PRs

For an existing component branch or unmerged PR, follow
[How to use the blueos repository](./how-to-use-blueos-repo.md) to import
the branch and integrate it with the complete central history before
continuing development and publishing a central PR. Include any unmerged
dependencies in the same central branch.

After publishing the replacement central PR, close the original component
PR and link to the replacement to avoid merging the same work twice. If
the original branch is shared, agree on the migration and where further
development will take place first.
