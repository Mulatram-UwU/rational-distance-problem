set -x
date
lake update 2>&1 | tail -30
echo "=== UPDATE DONE ==="
lake exe cache get 2>&1 | tail -30
echo "=== CACHE DONE ==="
date
