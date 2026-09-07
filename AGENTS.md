# Repository Guidelines

## Project Structure & Module Organization
`app/` contains the Flask application, HTML templates, static assets, migrations, and feature modules such as `downloads/`, `library.py`, `titles.py`, and `settings.py`. The downloads integrations live under `app/downloads/` (`client.py`, `manager.py`, `prowlarr.py`, `torrent_client.py`, `usenet_client.py`). The main entrypoint is `app/app.py`. Tests live in `tests/` and follow focused module-based coverage such as `test_download_clients.py`, `test_library_helpers.py`, `test_library_settings_validation.py`, `test_settings_keys_cache.py`, `test_proxy_trust.py`, and `test_titledb_resilience.py`. Deployment files are at the repo root (`Dockerfile`, `docker-compose.yml`, `docker-compose.dev.yml`), with helper scripts in `tools/`, `Start.bat`, and `start.sh`.

## Build, Test, and Development Commands
Install dependencies with:

```bash
pip install -r requirements.txt
```

Run locally with:

```bash
python app/app.py
```

On Windows, `Start.bat` reuses or generates and persists the application secret key, then starts `app/app.py` with `python.exe`. Install dependencies in your selected Python environment before running it; the script does not create a virtual environment, install dependencies, or pull changes. On Unix-like systems, `./start.sh` exports bootstrap credentials and runs `python app/app.py`.

Run all tests with:

```bash
python -m unittest discover -s tests
```

Run a focused suite while iterating:

```bash
python -m unittest discover -s tests -p "test_download_clients.py"
```

Use Docker when validating container behavior:

```bash
docker compose -f docker-compose.dev.yml up --build
```

## Coding Style & Naming Conventions
Use 4-space indentation and keep Python code straightforward rather than overly abstract. Follow existing naming patterns: `snake_case` for functions and variables, `UPPER_CASE` for constants, and `CamelCase` for test classes. Prefer small helper functions in `app/` modules over duplicating logic in routes. Keep template JavaScript defensive around nullable API fields.

## Testing Guidelines
Tests use the standard library `unittest` framework with `unittest.mock.patch`. Add or update targeted tests for every behavioral fix, especially around downloads, queue state handling, library organization, settings validation, and request handling. Name new files `tests/test_<area>.py` and keep tests deterministic and filesystem-light where possible. For temporary files, use the repository-local `.tmp/` directory instead of system temp directories, especially on Windows. Use synthetic fixture data only: no real game names, personal directories, or production-like local paths in tests. Prefer placeholders such as `Example Title`, `Example Release NSW-GRP`, and `X:\fixture-root\...`.

## Commit & Pull Request Guidelines
Inspect Git status before editing. Preserve unrelated changes, avoid whole-file formatting or line-ending conversion, and stage only changes belonging to the current task.

Match the existing history: short imperative Conventional Commit style subjects. Keep commits scoped to one change. If an issue number is given, include it in the commit msg. PRs should describe the user-visible impact, note any config or migration implications, link related issues, and include screenshots for UI/template changes. When a branch touches downloads or library management, mention protocol/client support, queue behavior, cleanup actions, and the focused unittest commands that cover the change.
Use non-interactive Git editor flows by default. Prefer commands such as `git commit --no-edit` or explicitly setting a no-op editor instead of opening an interactive editor during rebases, merges, or other automated Git steps.
When creating a fix branch from `upstream/dev`, do not leave the branch tracking `upstream/dev`. After branch creation, either unset the upstream or push with `-u origin <branch>` so the branch tracks its matching `origin/...` branch instead of the shared base branch.

## Security & Configuration Tips
Do not commit secrets, `keys.txt`, or real API credentials. Prefer `AEROFOIL_*` environment variables over legacy `OWNFOIL_*` names. For production, set a strong `AEROFOIL_SECRET_KEY` and validate proxy settings before enabling trusted forwarded headers.
