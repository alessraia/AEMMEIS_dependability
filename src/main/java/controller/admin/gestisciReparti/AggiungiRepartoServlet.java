package controller.admin.gestisciReparti;

import controller.utils.ControlMethod;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/aggiungi-reparto")
public class AggiungiRepartoServlet extends HttpServlet {
    private RepartoDAO repartoService;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.repartoService = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        Reparto reparto = new Reparto();
        String nome = request.getParameter("nome");
        String descrizione = request.getParameter("descrizione");
        String immagine = request.getParameter("immagine");
        
        // Trim parameters to remove leading/trailing whitespace
        if(nome != null) nome = nome.trim();
        if(descrizione != null) descrizione = descrizione.trim();
        if(immagine != null) immagine = immagine.trim();
        
        if(nome==null || nome.isEmpty() || descrizione==null || descrizione.isEmpty() || immagine==null || immagine.isEmpty()){
            //pagina di errore per inserimento parametri errato
            ControlMethod.safeRedirect(response, "/WEB-INF/errorJsp/erroreForm.jsp", this);
            return;
        }

        reparto.setDescrizione(descrizione);
        reparto.setNome(nome);
        reparto.setImmagine(immagine);

        if (repartoService == null) {
            repartoService = new RepartoDAO();
        }
        List<Reparto> reparti= repartoService.doRetrivedAll();
        boolean flag=true;
        for (Reparto rep:reparti){
            if(rep.getNome().equals(reparto.getNome())){
                request.setAttribute("esito", "non riuscito");//per poter mostrare un errore nell'inserimento
                RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/reparti/aggiungiReparto.jsp");
                try {
                    dispatcher.forward(request, response);
                } catch (ServletException e) {
                    log("Errore durante il forward ", e);
                } catch (IOException e) {
                    log("Errore di I/O durante il forward", e);
                }
                flag=false;
            }
        }
        if(flag) {
            repartoService.doSave(reparto);
            ControlMethod.safeRedirect(response,"gestisci-reparti", this);
        }

    }
}
