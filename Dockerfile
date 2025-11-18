# === STAGE 1: build della webapp con Maven ===
FROM maven:3.9.6-eclipse-temurin-11 AS build
WORKDIR /app

# Copio solo il pom e scarico le dipendenze (cache più efficiente)
COPY pom.xml .
RUN mvn -B dependency:go-offline

# Copio il sorgente e compilo
COPY src ./src
RUN mvn -B package -DskipTests

# === STAGE 2: runtime con Tomcat ===
FROM tomcat:10.1-jdk11-temurin

# Pulisco le webapp di default
RUN rm -rf /usr/local/tomcat/webapps/*

# Copio il WAR generato nello stage di build e lo chiamo ROOT.war
# (così l'app è raggiungibile su http://localhost:8080/)
COPY --from=build /app/target/AEMMETSW-1.0-SNAPSHOT.war /usr/local/tomcat/webapps/ROOT.war

EXPOSE 8080

# Avvio Tomcat
CMD ["catalina.sh", "run"]

