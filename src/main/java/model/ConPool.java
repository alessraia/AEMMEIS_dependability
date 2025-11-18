/*
BSD 3-Clause License

Copyright (c) 2019, Mattia De Rosa
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.

* Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/
package model;

import org.apache.tomcat.jdbc.pool.DataSource;
import org.apache.tomcat.jdbc.pool.PoolProperties;

import java.sql.Connection;
import java.sql.SQLException;
import java.util.TimeZone;

public class ConPool {
	private static DataSource datasource;

	public static Connection getConnection() throws SQLException {
		if (datasource == null) {
			PoolProperties p = new PoolProperties();

			String dbHost = getEnvOrDefault("DB_HOST", "localhost");
			String dbPort = getEnvOrDefault("DB_PORT", "3306");
			String dbName = getEnvOrDefault("DB_NAME", "aemmetsw");
			String dbUser = getEnvOrDefault("DB_USER", "root");
			String dbPass = getEnvOrDefault("DB_PASS", "aless04");

			String tz = TimeZone.getDefault().getID();
			p.setUrl("jdbc:mysql://" + dbHost + ":" + dbPort + "/" + dbName + "?serverTimezone=" + tz);
			p.setDriverClassName("com.mysql.cj.jdbc.Driver");
			p.setUsername(dbUser);
			p.setPassword(dbPass);

			p.setMaxActive(100);
			p.setInitialSize(10);
			p.setMinIdle(10);
			p.setRemoveAbandonedTimeout(60);
			p.setRemoveAbandoned(true);
			datasource = new DataSource();
			datasource.setPoolProperties(p);

		}
		return datasource.getConnection();
	}

	private static String getEnvOrDefault(String key, String defaultValue) {
		String value = System.getenv(key);
		if (value == null || value.isBlank()) {
			return defaultValue;
		}
		return value;
	}
}
