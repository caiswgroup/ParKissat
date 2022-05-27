################### Use Mallob
FROM parkissat-base AS builder
USER root

################### Extract Mallob in run stage
FROM satcomp-base:worker AS parkissat_liaison
WORKDIR /
# Copy parkissat
COPY --from=builder /parkissat/parkissat parkissat
COPY --chown=ecs-user /worker /competition

RUN chmod +x /competition/worker
