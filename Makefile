all:
	@make ide

clean:
	rm -f src/.*.aux src/*.vo src/*.glob

image:
	docker-compose build

ide: image
	docker-compose up
