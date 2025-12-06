package controller.utente;

import controller.utils.ControlMethod;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;

@WebServlet("/rimuovi-telefono")
public class RimuoviTelefonoServlet extends HttpServlet {
    private UtenteDAO utenteDAO;

    // Permette ai test di iniettare un mock di UtenteDAO
    public void setUtenteDAO(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        // JSON parser object to parse read JSON data from request
        JSONParser jsonParser = new JSONParser();
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");

        try (InputStreamReader reader = new InputStreamReader(request.getInputStream())) {
            // Parse JSON data
            Object obj = jsonParser.parse(reader);
            JSONObject item = (JSONObject) obj;

            // Ottieni i valori da JSON
            String email = (String) item.get("email");
            String telefono = (String) item.get("telefono");

            // Chiamata alla funzione del DAO per rimuovere il telefono (usa istanza iniettata per i test)
            UtenteDAO service = this.utenteDAO != null ? this.utenteDAO : new UtenteDAO();
            List<String> telefoni = service.cercaTelefoni(email);
            if(telefoni.contains(telefono)) {
                service.deleteTelefono(email, telefono);
            }
            List<String> telefoniSession = utente.getTelefoni();
            boolean flag=true;
            for(int i=0; i < telefoniSession.size() && flag; i++){
                if(telefoniSession.get(i).equals(telefono)) {
                    telefoniSession.remove(i);
                    flag=false;
                }
            }
            session.setAttribute("utente", utente);


            // Invia una risposta al client
            response.setContentType("text/plain");
            response.setCharacterEncoding("UTF-8");
            response.getWriter().write("Telefono rimosso con successo.");
        } catch (IOException e) {
            ControlMethod.safeSendError(response, HttpServletResponse.SC_BAD_REQUEST, "Errore nella lettura della richiesta", this);
            return;
        } catch (ParseException e) {
            response.setStatus(HttpServletResponse.SC_BAD_REQUEST);
            response.getWriter().write("Errore nella lettura del JSON.");
        }
    }
}