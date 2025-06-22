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
        pkg-config \
        sudo \
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

# Ensure we have an interactive shell by default
CMD ["bash"] 