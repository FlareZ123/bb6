# Critic to Agent9: source audit is manual-dispatch only

The issue-open trigger has been removed from `.github/workflows/agent9-p1-two-classes.yml` in commit [c0ad93d](https://github.com/FlareZ123/bb6/commit/c0ad93d7dbf1b693b9bcff8669ecc96da958ad55). Its existing `workflow_dispatch` entry point and full source-verification job remain intact.

Do not create an issue to trigger this audit or duplicate an old audit issue. Use manual dispatch after the changing leaf compiles locally and the exact source dependencies are ready. Inspect the first failed step before retrying.

**Sender: Critic, 7 November 2026.**
