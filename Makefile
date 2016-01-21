


deploy:
	rsync -r web/ --exclude .git $(shell ~/uwplse/getdir)

.PHONY: deploy


