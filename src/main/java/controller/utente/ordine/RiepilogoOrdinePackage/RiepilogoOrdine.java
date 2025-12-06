package controller.utente.ordine.RiepilogoOrdinePackage;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.ordineService.RigaOrdine;
import model.ordineService.RigaOrdineDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.List;

@WebServlet("/riepilogo-ordine")
public class RiepilogoOrdine extends HttpServlet {

    // DAO eventualmente iniettato dai test
    private OrdineDAO ordineDAO;

    // Service con la logica di business
    private final RiepilogoOrdineService riepilogoOrdineService = new RiepilogoOrdineService();

    /**
     * Permette ai test di iniettare un mock di OrdineDAO.
     * Rimane compatibile con il tuo codice esistente.
     */
    public void setOrdineDAO(OrdineDAO ordineDAO) {
        this.ordineDAO = ordineDAO;
    }

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");

        // DAO da usare: se il test ne ha iniettato uno, usa quello; altrimenti istanza di default
        OrdineDAO dao = (this.ordineDAO != null) ? this.ordineDAO : new OrdineDAO();

        // idOrdine dai parametri (come prima, usato solo nel ramo non admin)
        String idOrdine = request.getParameter("idOrdine");

        // Logica delegata al service
        RiepilogoOrdineService.Result result =
                riepilogoOrdineService.preparaDati(utente, idOrdine, dao);

        if (result.isAdmin()) {
            // Ramo admin: identico al comportamento originale
            RequestDispatcher dispatcher =
                    request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward", e);
            }
            return;
        }

        // Ramo utente non admin: salvo l'ordine in sessione e vado alla JSP di riepilogo
        Ordine ordine = result.getOrdine();
        session.setAttribute("ordine", ordine);

        RequestDispatcher dispatcher =
                request.getRequestDispatcher("/WEB-INF/results/areaPservices/riepilogoOrdine.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }
}
