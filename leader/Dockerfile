################### Use Mallob
FROM parkissat-base AS builder
USER root


################### Extract parkissat in run stage
FROM satcomp-base:leader AS parkissat_liaison
WORKDIR /
# Copy parkissat and solver scripts
COPY --from=builder parkissat/parkissat parkissat
COPY --chown=ecs-user /run_parkissat.sh /competition
COPY --chown=ecs-user /solver /competition
USER ecs-user
RUN chmod +x /competition/run_parkissat.sh
RUN chmod +x /competition/solver