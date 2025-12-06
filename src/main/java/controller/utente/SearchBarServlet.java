package controller.utente;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

@WebServlet ("/search")
public class SearchBarServlet extends HttpServlet {
    private static final long serialVersionUID = 1L;
    private LibroDAO libroDAO;

    // Permette ai test di iniettare un mock di LibroDAO
    public void setLibroDAO(LibroDAO libroDAO) {
        this.libroDAO = libroDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);
            }
            return;
        }
        String query = request.getParameter("q");
    // usa l'istanza iniettata (per i test) o crea una nuova istanza di default
    LibroDAO libroService = this.libroDAO != null ? this.libroDAO : new LibroDAO();

        JSONArray jsonArray = new JSONArray();

        if (query != null && !query.trim().isEmpty()) {
            List<Libro> results = libroService.Search(query);
            // Creare un JSONArray dai risultati

            for (int i = 0; i < results.size() && i < 10; i++) {
                JSONObject jsonObject = new JSONObject();
                jsonObject.put("isbn", results.get(i).getIsbn());
                jsonObject.put("titolo", results.get(i).getTitolo());
                jsonArray.add(jsonObject);
            }
        }

        // Impostare il tipo di contenuto della risposta
        response.setContentType("application/json");
        response.setCharacterEncoding("UTF-8");

        // Inviare la risposta JSON al client
        PrintWriter out = response.getWriter();
        out.print(jsonArray);
        out.flush();


        // Simula una ricerca nei dati
        /*List<Libro> results = new ArrayList<>();
        if (query != null && !query.trim().isEmpty()) {
            List<Libro> risultati = libroService.Search(query);
            for (int i = 0; i< risultati.size() || i < 10; i++) {
                results.add(risultati.get(i));
            }
        }

        response.setContentType("text/html;charset=UTF-8");
        PrintWriter out = response.getWriter();

        if (!results.isEmpty()) {
            for (String result : results) {
                out.println("<div class='search-result-item'>" + result + "</div>");
            }
        } else {
            out.println("<div class='search-result-item'>Nessun risultato trovato</div>");
        }*/
    }
}
