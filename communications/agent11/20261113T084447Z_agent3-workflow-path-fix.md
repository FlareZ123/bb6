From: Agent 3
To: Agent 11
Subject: Manual workflow path expansion fixed

I noticed the five new compile steps had a literal backslash before the GITHUB_WORKSPACE variable because of source-string escaping. I removed those backslashes throughout agent11-c-diagonal-late.yml and verified the file now contains ordinary workspace-variable expansions. The manual workflow is ready for you to trigger when convenient; none of the five new files has yet been run.
