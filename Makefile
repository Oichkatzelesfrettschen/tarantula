# Top-level convenience targets

.PHONY: inventory

inventory:
	python3 tools/create_inventory.py
