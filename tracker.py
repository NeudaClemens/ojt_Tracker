import tempfile

# Debounce interval in seconds
DEBOUNCE_INTERVAL = 1.0

# Store pending saves
pending_saves = []
last_save_time = 0

# Atomic writing helper function

def atomic_write(file_path, data):
    with tempfile.NamedTemporaryFile('w', delete=False) as temp_file:
        temp_file.write(data)
        temp_file.flush()
        os.fsync(temp_file.fileno())
        os.rename(temp_file.name, file_path)

# Debounced save helpers

def debounced_save():
    global last_save_time
    now = time.time()
    if now - last_save_time >= DEBOUNCE_INTERVAL:
        save_records()
        last_save_time = now

def save_records():
    # Logic for saving records
    atomic_write('records.json', json.dumps(records))

# Inside _save_records

def _save_records(...):
    mark_dirty()

# Inside _load_records, adapting header detection

def _load_records(...):
    ... # your existing logic
    headers = [header.lower() for header in data[0]]  # case-insensitive header detection
    
# Update the save calls
#  Call _mark_dirty where appropriate instead of _save_records

# other existing methods and logic here
