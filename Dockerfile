# syntax=docker/dockerfile:1.4

FROM ubuntu:24.04

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# -----------------------------------------------------------------------------
# Install base build dependencies
# -----------------------------------------------------------------------------
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        build-essential \
        ca-certificates \
        curl \
        git \
        less \
        pkg-config \
        sudo \
        vim \
    && rm -rf /var/lib/apt/lists/*

# -----------------------------------------------------------------------------
# Configure and install mise
# -----------------------------------------------------------------------------
# mise stores all of its data/config/cache in /mise so it is easy to mount or cache
ENV MISE_DATA_DIR="/mise" \
    MISE_CONFIG_DIR="/mise" \
    MISE_CACHE_DIR="/mise/cache" \
    MISE_INSTALL_PATH="/usr/local/bin/mise" \
    PATH="/mise/shims:/usr/local/bin:${PATH}"

# Install the latest stable version of mise
RUN curl https://mise.run | sh && \
    echo 'eval "$(/usr/local/bin/mise activate bash --shims)"' >> ~/.bash_profile && \
    echo 'eval "$(/usr/local/bin/mise activate bash)"' >> ~/.bashrc && \
    mise doctor && \
    mise version

COPY mise.toml mise.lock Justfile pyproject.toml uv.lock ruff.toml ./
RUN --mount=type=secret,id=github_token \
    export GITHUB_TOKEN="$(cat /run/secrets/github_token)" && \
    mise trust \
    && mise install \
    && mise x -- just setup

# use heredoc to set up $HOME/.jjconfig.toml
RUN cat <<EOF > $HOME/.jjconfig.toml
[user]
name = "Cursor"
email = "user@host.com"

[git]
auto-local-bookmarks = true
push-new-bookmarks = true

[revset-aliases]
'closest_bookmark(to)' = 'heads(::to & bookmarks())'

# set all remote bookmarks (commits pushed to remote branches) to be immutable
'immutable_heads()' = "builtin_immutable_heads() & remote_bookmarks()"

[aliases]
dds = ["diff", "--tool", "difft-s"]
ddi = ["diff", "--tool", "difft-i"]
di = ["diff", "--tool", "idea"]
sm = ["b", "s", "main"]
smb = ["b", "s", "main", "-B"]
gp = ["git", "push"]
gf = ["git", "fetch"]
gpn = ["git", "push", "--allow-new"]
tug = ["bookmark", "move", "--from", "closest_bookmark(@-)", "--to", "@-"]

# Quick view of your current branch
l = ["log", "-r", "@ | @- | trunk()"]

# View all immutable heads, and trunk
li = ["log", "-r", "@ | immutable_heads() | trunk()"]

# See the path between your working copy and master
path = ["log", "-r", "@ | trunk() | remote_bookmarks('main') | remote_bookmarks('master')"]

[templates]
log = '''
  if(root,
    format_root_commit(self),
    label(if(current_working_copy, "working_copy"),
      concat(
        separate(" ",
          format_short_change_id_with_hidden_and_divergent_info(self),
          if(empty, label("empty", "(empty)")),
          if(description,
            description.first_line(),
            label(if(empty, "empty"), description_placeholder),
          ),
          bookmarks,
          tags,
          working_copies,
          if(git_head, label("git_head", "HEAD")),
          if(conflict, label("conflict", "conflict")),
          if(config("ui.show-cryptographic-signatures").as_boolean(),
            format_short_cryptographic_signature(signature)),
        ) ++ "\n",
      ),
    )
  )
'''
EOF

# Ensure we have an interactive shell by default
CMD ["bash"] 