package controller.utente;

import com.oracle.wls.shaded.org.apache.xml.utils.SystemIDResolver;
import controller.utils.ControlMethod;
import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.AggiornaCarrelloService;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.utenteService.Utente;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import javax.script.ScriptContext;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

@WebServlet("/aggiorna-carrello")
public class AggiornaCartServlet extends HttpServlet {

    // 🔹 Service riusabile, inizializzato una sola volta
    private final AggiornaCarrelloService aggiornaCarrelloService = new AggiornaCarrelloService();

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if (Validator.checkIfUserAdmin(utente)) {
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

        Carrello carrello = (Carrello) session.getAttribute("carrello");

        if (carrello == null) {
            ControlMethod.safeSendError(response, HttpServletResponse.SC_BAD_REQUEST, "Carrello non trovato", this);
            return;
        }

        JSONParser jsonParser = new JSONParser();

        try (InputStreamReader reader = new InputStreamReader(request.getInputStream())) {
            Object obj = jsonParser.parse(reader);
            JSONObject item = (JSONObject) obj;

            String isbn = (String) item.get("isbn");
            long quantityLong = (long) item.get("quantity");
            int quantity = (int) quantityLong;

            // 🔹 Logica spostata nel service
            boolean itemFound = aggiornaCarrelloService.aggiornaQuantita(carrello, isbn, quantity);


            if (!itemFound) {
                ControlMethod.safeSendError(response, HttpServletResponse.SC_BAD_REQUEST, "Elemento non trovato nel carrello.", this);
                return;
            }

            session.setAttribute("carrello", carrello);
            response.setStatus(HttpServletResponse.SC_OK);
        } catch (IOException e) {
            ControlMethod.safeSendError(response, HttpServletResponse.SC_BAD_REQUEST, "Errore nella lettura della richiesta", this);
            return;
        } catch (ParseException e) {
            ControlMethod.safeSendError(response, HttpServletResponse.SC_BAD_REQUEST, e.getMessage(), this);
            e.printStackTrace();
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            this.doGet(req, resp);
        } catch (ServletException | IOException e) {
            log("Errore durante la gestione POST (doGet)", e);
        }
    }
}
