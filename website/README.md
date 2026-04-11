# Verso Website

The website for [Verso](https://github.com/leanprover/verso), built
using Verso itself. The main page content is in
[`Site/FrontPage.lean`](Site/FrontPage.lean) and the HTML theme is
defined in [`Main.lean`](Main.lean).

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version
manager).

```sh
lake build
```

## Generating HTML

```sh
lake exe generate-site
```

The output is written to `_site/`. Serve it with a local web server to
view correctly:

```sh
cd _site && python3 -m http.server
```

## Deployment

Pushing to `main` automatically triggers a deployment of the website.

## Development

### Formatting

This project uses [Prettier](https://prettier.io/) for formatting CSS,
Markdown, and YAML files.

```sh
npm install
npx prettier --check .
npx prettier --write .  # to auto-fix
```

### Conventions

- All `.lean` files must start with a copyright header
- PR titles must follow the commit convention: `<type>: <subject>`
    - Allowed types: `feat`, `fix`, `doc`, `style`, `refactor`,
      `test`, `chore`, `perf`

## License

Apache 2.0 — see [LICENSE](LICENSE).
