package benchmark.util;

import model.libroService.Libro;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

import java.util.List;

/**
 * Helper usato SOLO nei benchmark JMH per replicare
 * la logica della SearchBarServlet che trasforma
 * una lista di Libro in un JSONArray con i campi
 * "isbn" e "titolo" (max 10 elementi).
 */
public class SearchBarJsonBuilderForBenchmark {

    /**
     * Costruisce un JSONArray a partire da una lista di libri,
     * limitando il numero di elementi a maxResults.
     */
    public JSONArray buildJsonArray(List<Libro> results, int maxResults) {
        JSONArray jsonArray = new JSONArray();

        int limit = Math.min(results.size(), maxResults);
        for (int i = 0; i < limit; i++) {
            Libro libro = results.get(i);
            JSONObject jsonObject = new JSONObject();
            jsonObject.put("isbn", libro.getIsbn());
            jsonObject.put("titolo", libro.getTitolo());
            jsonArray.add(jsonObject);
        }

        return jsonArray;
    }

    /**
     * Variante che restituisce direttamente la stringa JSON,
     * utile per avvicinarsi al comportamento della servlet.
     */
    public String buildJsonString(List<Libro> results, int maxResults) {
        return buildJsonArray(results, maxResults).toJSONString();
    }
}
